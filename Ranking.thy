theory Ranking
  imports 
    "AGF.Berge"
    "AGF.Bipartite"
    "List-Index.List_Index"
begin

sledgehammer_params [provers = e z3 spass cvc4 vampire]

lemma vs_empty[simp]: "Vs {} = {}"
  by (simp add: Vs_def)

lemma vs_insert: "Vs (insert e E) = e \<union> Vs E"
  unfolding Vs_def by simp

lemma vs_union: "Vs (A \<union> B) = Vs A \<union> Vs B"
  unfolding Vs_def by simp

lemma vs_compr: "Vs {{u, v} |v. v \<in> ns} = (if ns = {} then {} else {u} \<union> ns)"
  unfolding Vs_def by auto



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

lemma partitioned_bipartite_insertI:
  assumes "partitioned_bipartite E X"
  assumes "u \<notin> X" "v \<in> X"
  shows "partitioned_bipartite (insert {u,v} E) X"
  using assms
  apply (intro partitioned_bipartiteI)
   apply (drule partitioned_bipartite_graph_absD)
  by (auto simp: vs_insert elim!: partitioned_bipartiteE intro: graph_abs_insert dest: partitioned_bipartite_graph_absD)

lemma partitioned_bipartite_union:
  assumes "partitioned_bipartite G X"
  assumes "partitioned_bipartite H X"
  shows "partitioned_bipartite (G \<union> H) X"
  using assms partitioned_bipartite_graph_absD
  by (auto intro!: partitioned_bipartiteI intro: graph_abs_union simp: vs_union)
     (meson DiffD1 DiffD2 partitioned_bipartiteE)+

lemma partitioned_bipartite_compr:
  assumes "u \<notin> X" "u \<notin> Y" "finite X" "X \<subseteq> Y"
  shows "partitioned_bipartite {{u,v} |v. v \<in> X} Y"
  using assms
  by (intro partitioned_bipartiteI)
     (auto simp: graph_abs_compr vs_compr)
  

type_synonym 'a graph = "'a set set"


abbreviation "rank \<sigma> v \<equiv> index \<sigma> v"
abbreviation "arrival \<equiv> index \<circ> map fst"


lemma index_Cons_mono: "x \<noteq> y \<Longrightarrow> index xs y \<le> index (x#xs) y"
  by simp

lemma index_filter_mono: "P x \<Longrightarrow> index (filter P xs) x \<le> index xs x"
  by (induction xs) auto

lemma index_append_mono: "index xs x \<le> index (xs @ ys) x" 
  unfolding index_def
  by (auto simp: find_index_append find_index_le_size trans_le_add1)

abbreviation "arriving_U us \<equiv> fst ` set us"
abbreviation "arriving_V us \<equiv> \<Union> (snd ` set us)"

definition wf_input :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> bool" where
  "wf_input \<sigma> us \<equiv> 
    set \<sigma> \<inter> arriving_U us = {} \<and> 
    arriving_V us \<subseteq> set \<sigma> \<and>
    distinct \<sigma> \<and> 
    distinct (map fst us)"

lemma wf_input_distinctD:
  assumes "wf_input \<sigma> us"
  shows "distinct \<sigma>"
  using assms
  unfolding wf_input_def by auto

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

lemma ranking_aux_is_foldl:
  "ranking_aux \<sigma> us M = foldl (\<lambda>M' (u,ns). step \<sigma> M' u ns) M us"
  by (induction \<sigma> us M rule: ranking_aux.induct) (auto)

lemma ranking_aux_append_us:
  "ranking_aux \<sigma> (us@us') M = ranking_aux \<sigma> us' (ranking_aux \<sigma> us M)"
  by (simp add: ranking_aux_is_foldl)

definition ranking :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a graph" where
  "ranking \<sigma> us = ranking_aux \<sigma> us {}"

lemma ranking_is_foldl:
  "ranking \<sigma> us = foldl (\<lambda>M (u,ns). step \<sigma> M u ns) {} us"
  by (simp add: ranking_def ranking_aux_is_foldl)

lemma ranking_append_us:
  "ranking \<sigma> (us@us') = ranking_aux \<sigma> us' (ranking \<sigma> us)"
  by (simp add: ranking_aux_append_us ranking_def)

lemma ranking_PI: "P (ranking_aux \<sigma> us {}) \<Longrightarrow> P (ranking \<sigma> us)"
  unfolding ranking_def .

text \<open>The following invariant is maintained by the (steps of the) ranking algorithm.\<close>
\<comment> \<open>TODO: reconsider the wellformedness of the input in the invariant. It was put there, since the
   invariant is only preserved under (some conditions of) wellformedness.\<close>
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

lemma step_mono_Vs: "v \<in> Vs M \<Longrightarrow> v \<in> Vs (step \<sigma> M u ns)"
  by (auto intro: vs_transport dest: step_mono)

lemma ranking_aux_mono: "e \<in> M \<Longrightarrow> e \<in> ranking_aux \<sigma> us M"
  by (induction \<sigma> us M rule: ranking_aux.induct) (auto simp: step_mono)

lemma ranking_aux_mono_Vs: "v \<in> Vs M \<Longrightarrow> v \<in> Vs (ranking_aux \<sigma> us M)"
  by (auto intro: vs_transport dest: ranking_aux_mono)

lemma step_empty_if_no_neighbor: "set \<sigma> \<inter> ns = {} \<longleftrightarrow> step \<sigma> {} u ns = {}"
  by (induction \<sigma>) (auto simp: vs_member)

lemma step_no_neighbor: "set \<sigma> \<inter> ns = {} \<Longrightarrow> step \<sigma> M u ns = M"
  by (induction \<sigma>) auto

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
  shows "e \<in> M \<or> (\<exists>v. e = {u,v} \<and> (v \<in> ns \<inter> set \<sigma> - Vs M) \<and> (\<forall>v'\<in>ns \<inter> set \<sigma> - Vs M - {v}. rank \<sigma> v < rank \<sigma> v'))"
  using assms
  by (induction \<sigma> M u ns rule: step.induct) 
     (auto split: if_splits)

lemma edge_in_stepE:
  assumes "e \<in> step \<sigma> M u ns"
  assumes "e \<notin> M"
  obtains v where "e = {u,v}" "v \<in> ns \<inter> set \<sigma> - Vs M" "\<forall>v'\<in> ns \<inter> set \<sigma> - Vs M - {v}. rank \<sigma> v < rank \<sigma> v'"
  using assms
  by (auto dest: edge_in_step)


lemma edge_in_ranking_aux:
  assumes "e \<in> ranking_aux \<sigma> us M"
  shows "e \<in> M \<or> (\<exists>u ns v. (u,ns) \<in> set us \<and> e = {u,v} \<and> v \<in> ns \<inter> set \<sigma> - Vs M)" \<comment> \<open>The property on v not being in \<^term>\<open>Vs M\<close> is probably not strong enough to be useful.\<close>
  using assms
  by (induction \<sigma> us M rule: ranking_aux.induct)
     (auto dest!: edge_in_step step_mono_Vs)

lemma edge_in_ranking_auxE:
  assumes "e \<in> ranking_aux \<sigma> us M"
  assumes "e \<notin> M"
  obtains u ns v where "(u,ns) \<in> set us" "e = {u,v}" "v \<in> ns \<inter> set \<sigma> - Vs M"
  using assms
  by (auto dest: edge_in_ranking_aux)


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
  case (Cons v \<sigma>)
  then have graph_abs: "graph_abs (step \<sigma> M u ns)"
    by (auto dest: partitioned_bipartite_graph_absD intro: graph_abs_step)
  show ?case
  proof (rule step_ConsI)
    assume "v \<in> ns" "v \<notin> Vs M"
    with Cons.prems show "partitioned_bipartite (insert {u,v} M) (set (v#\<sigma>))"
      by (auto intro: partitioned_bipartite_insertI)
  next
    assume "v \<notin> ns \<or> v \<in> Vs M"
    then show "partitioned_bipartite (step \<sigma> M u ns) (set (v#\<sigma>))"
      by (intro partitioned_bipartiteI[OF graph_abs])
         (smt (verit, del_insts) Cons.prems(1) Cons.prems(2) Diff_iff IntE edge_in_step edges_are_Vs insertCI insert_commute list.set(2) partitioned_bipartiteE)
  qed
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


lemma graph_abs_ranking_aux:
  assumes "graph_abs M"
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  shows "graph_abs (ranking_aux \<sigma> us M)"
  using assms
  by (induction us arbitrary: M) (auto simp: graph_abs_step)


lemma matching_ranking_aux:
  assumes "graph_abs M"
  assumes "matching M"
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "arriving_U us \<inter> Vs M = {}"
  assumes "distinct (map fst us)"
  shows "matching (ranking_aux \<sigma> us M)"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u ns us M)
  then have 1: "graph_abs (step \<sigma> M u ns)" "matching (step \<sigma> M u ns)"
    by (auto intro: graph_abs_step matching_step)

  have disjoint': "arriving_U us \<inter> ({u} \<union> set \<sigma> \<union> Vs M) = {}"
    using "2.prems"
    by (simp add: Int_Un_distrib Int_commute)

  then have "arriving_U us \<inter> Vs (step \<sigma> M u ns) = {}"
    by (smt (z3) Int_Un_distrib disjoint_iff insertCI sup_bot.neutr_eq_iff vs_step)

  then show ?case
    using 2 1
    by auto
qed auto

lemma partitioned_bipartite_ranking_aux:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
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
  apply (auto intro!: ranking_invI matching_ranking_aux partitioned_bipartite_ranking_aux 
        dest: ranking_invD partitioned_bipartite_graph_absD wf_input_tl)
      apply (metis (no_types, hide_lams) disjoint_iff fst_conv image_iff wf_input_def)
     apply (metis (no_types, lifting) ex_in_conv imageE list.set(1) partitioned_bipartiteE ranking_invD(3) ranking_invD(4) subset_iff vs_member)
  using wf_input_def apply blast
   apply (metis disjoint_iff eq_fst_iff image_eqI wf_input_def)
  by (metis (no_types, lifting) DiffI empty_iff empty_set image_empty ranking_inv_subset_\<sigma> subset_eq vs_offline_graph vs_ranking_aux wf_input_def)

lemma graph_abs_ranking:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  shows "graph_abs (ranking \<sigma> us)"
  by (simp add: assms ranking_PI graph_abs_ranking_aux)

lemma matching_ranking:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "arriving_U us \<inter> Vs M = {}"
  assumes "distinct (map fst us)"
  shows "matching (ranking \<sigma> us)"
  using assms
  by (simp add: ranking_def matching_ranking_aux)


lemma partitioned_bipartite_ranking:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  shows "partitioned_bipartite (ranking \<sigma> us) (set \<sigma>)"
  using assms
  by (simp add: ranking_def partitioned_bipartite_ranking_aux)


lemma graph_abs_offline_graph:
  assumes "wf_input \<sigma> us"
  shows "graph_abs (offline_graph us)"
  using assms
  by (induction us rule: offline_graph.induct) 
     (auto dest: wf_input_tl wf_input_hd intro: graph_abs_union graph_abs_compr)

lemma partitioned_bipartite_offline_graph:
  assumes "wf_input \<sigma> us"
  shows "partitioned_bipartite (offline_graph us) (set \<sigma>)"
  using assms
proof (induction us rule: offline_graph.induct)
  case (2 u ns us)
  show ?case 
  proof (simp, intro partitioned_bipartite_union)
    show "partitioned_bipartite {{u,v} |v. v \<in> ns} (set \<sigma>)" using "2.prems"
      by (auto dest: wf_input_hd intro: partitioned_bipartite_compr)
  next
    show "partitioned_bipartite (offline_graph us) (set \<sigma>)" using 2
      by (auto dest: wf_input_tl)
  qed
qed auto


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
  assumes "distinct (map fst ((u',ns)#us))"
  assumes "set \<sigma> \<inter> arriving_U us = {}"
  assumes "v \<in> set \<sigma>"
  assumes "u \<notin> Vs (step \<sigma> M u' ns)"
  assumes "{u, v} \<in> ranking_aux \<sigma> ((u', ns) # us) M"
  shows "u \<noteq> u'"
proof (rule ccontr, simp)
  assume "u = u'"
  have "u \<notin> Vs M" using assms
    by (meson step_mono vs_transport)
  have "u \<notin> arriving_U us"
    by (metis (no_types, hide_lams) \<open>u = u'\<close> assms(1) distinct.simps(2) fst_conv list.simps(9) set_map)
  show False
    by (smt (verit, del_insts) \<open>u \<notin> arriving_U us\<close> assms(2) assms(3) assms(4) assms(5) disjoint_iff doubleton_eq_iff edge_in_ranking_aux fst_conv image_iff insertCI ranking_aux.simps(2) vs_member)
qed


lemma u_in_ranking_aux:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "v \<in> set \<sigma>"
  assumes "u \<notin> Vs M"
  assumes "{u,v} \<in> ranking_aux \<sigma> us M"
  shows "u \<in> arriving_U us - set \<sigma>"
  using assms
  by (auto dest!: edge_in_ranking_aux simp: doubleton_eq_iff intro!: rev_image_eqI)

lemma u_in_stepE:
  assumes "u \<in> Vs (step \<sigma> M u ns)"
  assumes "u \<notin> Vs M"
  assumes "u \<notin> set \<sigma>"
  obtains v where "u \<noteq> v" "{u,v} \<in> step \<sigma> M u ns" "v \<in> ns" "v \<in> set \<sigma>"
  using assms
  by (induction \<sigma> M u ns rule: step.induct) (auto split: if_splits)

lemma step_matches_u_if_possible:
  assumes "u \<notin> Vs M"
  assumes "\<exists>v. v \<in> set \<sigma> \<inter> ns - Vs M"
  shows "u \<in> Vs (step \<sigma> M u ns)"
  using assms
  apply (induction \<sigma> M u ns rule: step.induct)
   apply simp_all
  by (metis edges_are_Vs insertI1)

lemma neighbors_of_eq:
  assumes "distinct (map fst us)"
  assumes "(u,ns) \<in> set us"
  shows "neighbors_of u us = ns"
  using assms
proof (induction us rule: neighbors_of.induct)
  case (2 u v ns' vs)
  then show ?case 
  proof (cases "u = v")
    case True
    then show ?thesis 
      using 2
      by (auto intro: eq_key_imp_eq_value simp: rev_image_eqI)
  qed auto
qed simp

lemma u_in_step:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "arriving_U us \<inter> arriving_V us = {}"
  assumes "distinct (map fst us)"
  assumes "u \<notin> Vs M"
  assumes "v \<notin> Vs M"
  assumes "v \<in> set \<sigma> \<inter> neighbors_of u us"
  shows "u \<in> Vs (step \<sigma> M u (neighbors_of u us))"
  using assms
  by (metis Diff_iff step_matches_u_if_possible)

lemma vertex_in_step_edge_in_step:
  assumes "arriving_U ((u,ns)#us) \<inter> set \<sigma> = {}"
  assumes "distinct (map fst ((u, ns) # us))"
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
    using assms by force
  with assms obtain v' where "u \<noteq> v'" "{u,v'} \<in> step \<sigma> M u ns" "v' \<in> ns" "v' \<in> set \<sigma>"
    by (auto elim: u_in_stepE)
  have "v' = v" 
  proof (rule ccontr)
    assume "v' \<noteq> v"
    then have "{u,v'} \<in> ranking_aux \<sigma> ((u,ns)#us) M"
      by (simp add: \<open>{u, v'} \<in> step \<sigma> M u ns\<close> ranking_aux_mono)
    have "matching (ranking_aux \<sigma> ((u,ns)#us) M)"
      using assms
      by (intro matching_ranking_aux partitioned_bipartite_graph_absD)
    then show False 
      by (metis \<open>v' \<noteq> v\<close> \<open>{u, v'} \<in> ranking_aux \<sigma> ((u, ns) # us) M\<close> assms(9) doubleton_eq_iff insertI1 matching_unique_match)
  qed
  then show ?thesis
    using \<open>{u, v'} \<in> step \<sigma> M u ns\<close> by auto
qed


lemma arriving_U_disjoint_Cons:
  assumes "distinct (map fst ((u,ns)#us))"
  assumes "arriving_U ((u,ns)#us) \<inter> set \<sigma> = {}"
  assumes "arriving_U ((u,ns)#us) \<inter> Vs M = {}"
  shows "arriving_U us \<inter> Vs (step \<sigma> M u ns) = {}"
proof (rule ccontr)
  assume "arriving_U us \<inter> Vs (step \<sigma> M u ns) \<noteq> {}"
  then obtain u' where "u' \<in> arriving_U us" "u' \<in> Vs (step \<sigma> M u ns)"
    by blast
  then consider "u' = u" | "u' \<in> Vs M"
    using assms vs_step by fastforce
  then show False
  proof cases
    case 1
    then show ?thesis
      using \<open>u' \<in> arriving_U us\<close> assms by auto
  next
    case 2
    then show ?thesis
      using \<open>u' \<in> arriving_U us\<close> assms by fastforce
  qed
qed

lemma ranking_aux_lowest_rank:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "distinct (map fst us)"
  assumes "u \<notin> Vs M"
  assumes "v \<in> set \<sigma>" \<comment> \<open>hence, u is the node that arrives\<close>
  assumes w_unmatched: "w \<in> set \<sigma>" "w \<in> neighbors_of u us" "w \<notin> Vs M" "w \<notin> Vs (ranking_aux \<sigma> us M)"
  assumes uv_matched: "{u,v} \<in> ranking_aux \<sigma> us M"
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "matching M"
  assumes "arriving_U us \<inter> Vs M = {}"
  shows "rank \<sigma> v < rank \<sigma> w"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u' ns us M)
  have "u \<notin> set \<sigma>"
    by (meson "2.prems" DiffD2 u_in_ranking_aux)

  have "w \<noteq> v"
    using uv_matched insert_commute w_unmatched(4) by blast

  consider (ind) "u \<notin> Vs (step \<sigma> M u' ns)" | (new) "u \<in> Vs (step \<sigma> M u' ns)" by blast
  then show ?case
  proof cases
    case ind
    have "w \<in> set \<sigma>" 
      using "2.prems" by blast

    have "u \<noteq> u'"
      using "2.prems"(1) "2.prems"(2) "2.prems"(4) "2.prems"(9) ind ranking_aux_hd_ineq by fastforce

     have "w \<in> neighbors_of u us"
       by (rule neighbors_of_Cons[OF \<open>u \<noteq> u'\<close> "2.prems"(6)])

    have "w \<notin> Vs (step \<sigma> M u' ns)"
      by (metis (full_types) "2"(9) ranking_aux.simps(2) ranking_aux_mono vs_transport)

    have "arriving_U us \<inter> Vs (step \<sigma> M u' ns) = {}"
      by (meson "2.prems" arriving_U_disjoint_Cons)

    show ?thesis
      apply (rule "2.IH")
      using "2.prems"(1) apply simp
      apply (simp_all add: "2.prems" ind \<open>w \<in> neighbors_of u us\<close> \<open>w \<notin> Vs (step \<sigma> M u' ns)\<close> \<open>arriving_U us \<inter> Vs (step \<sigma> M u' ns) = {}\<close>)
      using "2.prems"(2) apply force
      using "2.prems"(8) apply force
      using "2.prems"(9) apply auto[1]
       apply (metis "2.prems"(1) "2.prems"(10) disjoint_iff fst_conv image_eqI list.set_intros(1) partitioned_bipartite_step)
      using "2.prems"(1) "2.prems"(11) "2.prems"(12) matching_step apply fastforce
      done
  next
    case new
    have "u' = u"
      by (metis "2.prems" \<open>u \<notin> set \<sigma>\<close> new vs_step)
    then have "{u,v} \<in> step \<sigma> M u ns"
      by (metis "2.prems" new vertex_in_step_edge_in_step)
    have "w \<in> ns"
      using "2.prems" \<open>u' = u\<close> by auto
    show ?thesis
      by (meson "2.prems" \<open>u \<notin> set \<sigma>\<close> \<open>w \<in> ns\<close> \<open>w \<noteq> v\<close> \<open>{u, v} \<in> step \<sigma> M u ns\<close> step_lowest_rank)
  qed
qed simp

theorem ranking_lowest_rank:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "distinct (map fst us)"
  assumes "v \<in> set \<sigma>"
  assumes "w \<in> set \<sigma>" "w \<in> neighbors_of u us" "w \<notin> Vs (ranking \<sigma> us)"
  assumes "{u,v} \<in> ranking \<sigma> us"
  shows "rank \<sigma> v < rank \<sigma> w"
  using assms
  by (intro ranking_aux_lowest_rank[where u = u and M = "{}"]) (simp_all add: ranking_def)


lemma ranking_aux_first_arrival:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "distinct (map fst us)"

  assumes "v \<in> set \<sigma>" "v \<in> neighbors_of u us"
  assumes "u \<in> arriving_U us" "u \<notin> Vs (ranking_aux \<sigma> us M)"
  assumes "{u',v} \<in> ranking_aux \<sigma> us M"

  assumes "u \<notin> Vs M" "u' \<notin> Vs M"
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "matching M"
  assumes "arriving_U us \<inter> Vs M = {}"

  shows "arrival us u' < arrival us u"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u'' ns us M)

  have "u \<noteq> u'"
    by (metis assms edges_are_Vs)

  have "v \<notin> Vs M"
    by (smt (verit, ccfv_SIG) "2.prems" disjoint_iff doubleton_eq_iff edge_in_ranking_aux fst_conv image_eqI insertCI vs_member_intro)

  have "u'' \<noteq> u"
  proof (rule ccontr, simp only: not_not)
    assume "u'' = u"
    then have "neighbors_of u ((u'',ns)#us) = ns" 
      by simp
    then have "u \<in> Vs (step \<sigma> M u ns)"
      apply (intro step_matches_u_if_possible)
       apply (simp add: "2.prems")
      by (metis "2.prems" Diff_iff IntI \<open>v \<notin> Vs M\<close> in_mono neighbors_of.simps(2) wf_input_hd)

    then have "u \<in> Vs (ranking_aux \<sigma> ((u'',ns)#us) M)"
      by (metis \<open>u'' = u\<close> ranking_aux.simps(2) ranking_aux_mono vs_member)
    then show False using "2.prems"
      by blast
  qed

  then consider (new) "u'' = u'" | (ind) "u'' \<noteq> u \<and> u'' \<noteq> u'" by blast
  then show ?case 
  proof cases
    case new
    then show ?thesis using \<open>u'' \<noteq> u\<close> by fastforce
  next
    case ind
    then show ?thesis
      apply (auto intro!: "2.IH"[simplified])
      using "2.prems"(1) apply fastforce
      using "2.prems"(2) apply auto[1]
               apply (simp add: "2.prems")
      using "2.prems"(4) apply force
      using "2.prems"(5) apply auto[1]
      using "2.prems"(6) apply fastforce
      using "2.prems"(7) apply force
          apply (metis "2.prems" ranking_aux.simps(2) ranking_aux_mono vs_member)
         apply (metis "2.prems" u_in_ranking_aux vs_step)
      using "2.prems"(1) "2.prems"(10) partitioned_bipartite_step apply fastforce
       apply (metis "2.prems" disjoint_iff fst_conv image_iff list.set_intros(1) matching_step wf_input_hd)
      by (smt (verit, ccfv_SIG) "2.prems" disjoint_iff distinct.simps(2) fst_conv image_iff insert_iff list.set(2) list.simps(9) set_map vs_step wf_input_def)
  qed
qed simp

theorem ranking_first_arrival:
  assumes "arriving_U us \<inter> set \<sigma> = {}"
  assumes "distinct (map fst us)"
  assumes "v \<in> set \<sigma>" "v \<in> neighbors_of u us"
  assumes "u \<in> arriving_U us" "u \<notin> Vs (ranking \<sigma> us)"
  assumes "{u',v} \<in> ranking \<sigma> us"
  shows "arrival us u' < arrival us u"
  using assms
  by (intro ranking_aux_first_arrival[where u = u and M = "{}"]) (simp_all add: ranking_def)


definition move_to :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_ \<mapsto>\<index> _" [100,100] 40) where 
  "move_to xs v i \<equiv> (take i [x <- xs. x \<noteq> v]) @ v # (drop i [x <- xs. x \<noteq> v])"

lemma append_cong: "xs = xs' \<Longrightarrow> ys = ys' \<Longrightarrow> xs @ ys = xs' @ ys'"
  by simp

lemma move_to_gt_length:
  "length xs \<le> i \<Longrightarrow> (v \<mapsto>\<^bsub>xs\<^esub> i) = (v \<mapsto>\<^bsub>xs\<^esub> length xs)"
  unfolding move_to_def
  by (auto intro!: append_cong dest: le_trans[OF length_filter_le])

lemma move_to_set: "set (x \<mapsto>\<^bsub>xs\<^esub> i) = set xs \<union> {x}"
  unfolding move_to_def
  apply (auto dest: in_set_takeD in_set_dropD)
  by (metis (mono_tags, lifting) append_take_drop_id filter_set last_index_append last_index_size_conv length_append member_filter)

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

lemma wf_input_move_to:
  assumes "wf_input \<sigma> us"
  assumes "v \<in> set \<sigma>"
  shows "wf_input (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) us"
  using assms
  unfolding wf_input_def
  by (auto simp: move_to_set move_to_distinct)


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
  "count_list \<sigma> v = (Suc 0) \<Longrightarrow> (v \<mapsto>\<^bsub>\<sigma>\<^esub> (rank \<sigma> v)) = \<sigma>"
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

lemma distinct_count_in_set: "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> count_list xs x = 1"
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

lemma
  assumes "distinct xs"
  assumes "xs = ps @ x # ss"
  assumes "i \<le> rank xs x"
  obtains pps pss where "(x \<mapsto>\<^bsub>xs\<^esub> i) = pps @ x # pss @ ss" "pps @ pss = ps"
  using assms
proof (induction xs i arbitrary: ps rule: induct_list_nat)
  case (cons_zero a xs)
  then show ?case
    by (auto simp: move_to_0 not_in_set_filter_id) blast
next
  case (cons_suc a xs n)
  consider (eq) "a = x" | (neq) "a \<noteq> x" by blast
  then show ?case
  proof cases
    case eq
    with cons_suc.prems have "ps = []" 
      by (auto simp: Cons_eq_append_conv)
    with cons_suc show ?thesis 
      by (auto simp: move_to_0 not_in_set_filter_id)
  next
    case neq

    with cons_suc.prems obtain tl_ps where "ps = a # tl_ps" 
      by (auto simp: Cons_eq_append_conv)

    with cons_suc.prems have "xs = tl_ps @ x # ss" 
      by simp

    have "distinct xs"
      using cons_suc.prems(2) by simp

    have "n \<le> rank xs x" 
      using cons_suc.prems(4) neq by auto

    then obtain pps pss where "(x \<mapsto>\<^bsub>xs\<^esub> n) = pps @ x # pss @ ss" "pps @ pss = tl_ps"
      thm cons_suc.IH
      sorry

    then show ?thesis sorry
  qed
qed auto

lemma step_append:
  "u \<notin> Vs M \<Longrightarrow> step (\<sigma> @ \<sigma>') M u ns = (if u \<in> Vs (step \<sigma> M u ns) then step \<sigma> M u ns else step \<sigma>' M u ns)"
  by (induction \<sigma> M u ns rule: step.induct) (simp_all add: Vs_def, fastforce)

lemma step_no_change:
  assumes "set \<sigma> \<inter> ns - Vs M = {}"
  shows "step \<sigma> M u ns = M"
  using assms 
  by (induction \<sigma> M u ns rule: step.induct) auto

lemma ranking_aux_append_vs:
  assumes "arriving_U us \<inter> set (\<sigma> @ \<sigma>') = {}"
  assumes "arriving_U us \<inter> arriving_V us = {}"
  assumes "distinct (map fst us)"
  assumes "arriving_U us \<inter> Vs M = {}"
  shows "ranking_aux (\<sigma> @ \<sigma>') us M = ranking_aux \<sigma>' [u <- us. fst u \<notin> Vs (ranking_aux \<sigma> us M)] (ranking_aux \<sigma> us M)"
  using assms
proof (induction us arbitrary: M)
  case (Cons a us)
  obtain u ns where a_pair: "a = (u,ns)" by fastforce
  then have "u \<notin> Vs M"
    using Cons.prems by fastforce

  have disjoint_step: "arriving_U us \<inter> Vs (step \<sigma> M u ns) = {}" 
    using Cons.prems
    unfolding a_pair
    by (simp add: Int_Un_distrib arriving_U_disjoint_Cons bot_eq_sup_iff)

  have disjoint_step': "arriving_U us \<inter> Vs (step (\<sigma> @ \<sigma>') M u ns) = {}"
    using Cons.prems
    unfolding a_pair
    by (simp add: Int_Un_distrib arriving_U_disjoint_Cons bot_eq_sup_iff)

  have neighbors: "neighbors_of u ((u,ns)#us) = ns" by simp

  have p1: "arriving_U us \<inter> set (\<sigma> @ \<sigma>') = {}"
    using Cons.prems(1) by force
  have p2: "arriving_U us \<inter> arriving_V us = {}"
    using Cons.prems(2) UnCI by fastforce
  have p3: "distinct (map fst us)" using Cons.prems by simp

  let ?r_pref = "(ranking_aux \<sigma> ((u,ns)#us) M)" and ?r_full = "(ranking_aux (\<sigma> @ \<sigma>') ((u,ns)#us) M)"

  consider (matched_prefix) "u \<in> Vs ?r_pref" | (matched_suffix) "u \<notin> Vs ?r_pref \<and> u \<in> Vs ?r_full" | 
    (not_matched) "u \<notin> Vs ?r_pref \<and> u \<notin> Vs ?r_full" by blast

  then show ?case 
  proof cases
    case matched_prefix
    then obtain v where "{u,v} \<in> ranking_aux \<sigma> ((u,ns)#us) M" "v \<notin> Vs M" "v \<in> ns \<inter> set \<sigma>"
      by (smt (verit, del_insts) Cons.prems(1) Cons.prems(3) IntE Int_Un_distrib \<open>u \<notin> Vs M\<close> a_pair distinct.simps(2) edge_in_ranking_aux fst_conv image_eqI insert_disjoint(1) insert_iff list.simps(15) list.simps(9) set_append set_map snd_conv sup_bot.neutr_eq_iff vs_member)
  
    have "u \<in> Vs (step \<sigma> M u ns)"
      apply (subst neighbors[symmetric])
      apply (rule u_in_step[where v=v])
           apply (metis Cons.prems(1) Int_Un_distrib a_pair set_append sup_bot.neutr_eq_iff)
      using Cons.prems(2) a_pair apply fastforce
      using Cons.prems(3) a_pair apply blast
        apply (simp add: \<open>u \<notin> Vs M\<close>)
       apply (simp add: \<open>v \<notin> Vs M\<close>)
      using \<open>v \<in> ns \<inter> set \<sigma>\<close> by auto

    with \<open>u \<notin> Vs M\<close> have step_append_eq: "step (\<sigma> @ \<sigma>') M u ns = step \<sigma> M u ns" by (simp add: step_append)

    with matched_prefix Cons.IH[OF p1 p2 p3 disjoint_step] show ?thesis
      by (auto simp: a_pair)
  next
    case matched_suffix
    then show ?thesis sorry
  next
    case not_matched
    then have "u \<notin> Vs (step \<sigma> M u ns)"
      by (metis (full_types) ranking_aux.simps(2) ranking_aux_mono vs_transport)

    then have step_M: "step \<sigma> M u ns = M"
      by (metis \<open>u \<notin> Vs M\<close> append_Nil2 step.simps(1) step_append)

    with \<open>u \<notin> Vs M\<close> have step_append_eq: "step (\<sigma> @ \<sigma>') M u ns = step \<sigma>' M u ns" by (simp add: step_append)

    from not_matched have "u \<notin> Vs (step \<sigma>' M u ns)"
      by (metis (full_types) ranking_aux.simps(2) ranking_aux_mono step_append_eq vs_transport)

    then have step'_M: "step \<sigma>' M u ns = M"
      by (metis \<open>u \<notin> Vs M\<close> append_Nil2 step.simps(1) step_append)

    have "u \<notin> Vs (ranking_aux \<sigma> us M)"
      using not_matched step_M by force

    have "u \<notin> Vs (step \<sigma>' (ranking_aux \<sigma> us M) u ns)"
    proof (rule ccontr, simp)
      assume "u \<in> Vs (step \<sigma>' (ranking_aux \<sigma> us M) u ns)"
      then have "u \<in> Vs (ranking_aux \<sigma>' ((u,ns)#us) (ranking_aux \<sigma> us M))"
        by (metis (full_types) ranking_aux.simps(2) ranking_aux_mono vs_transport)

      then have "u \<in> Vs (ranking_aux \<sigma>' ((u,ns)#us) M)" sorry

      then have "u \<in> Vs (ranking_aux (\<sigma> @ \<sigma>') ((u,ns)#us) M)" sorry
      then show False
        using not_matched by blast
    qed

    then have step'_ranking_aux: "step \<sigma>' (ranking_aux \<sigma> us M) u ns = ranking_aux \<sigma> us M" 
      apply (intro step_no_change)
    proof (rule ccontr)
      assume "u \<notin> Vs (step \<sigma>' (ranking_aux \<sigma> us M) u ns)" "set \<sigma>' \<inter> ns - Vs (ranking_aux \<sigma> us M) \<noteq> {}"
      then obtain v where "v \<in> set \<sigma>'" "v \<in> ns" "v \<notin> Vs (ranking_aux \<sigma> us M)" by blast
      then have "u \<in> Vs (step \<sigma>' (ranking_aux \<sigma> us M) u ns)"
        by (meson \<open>set \<sigma>' \<inter> ns - Vs (ranking_aux \<sigma> us M) \<noteq> {}\<close> \<open>u \<notin> Vs (ranking_aux \<sigma> us M)\<close> equals0I step_matches_u_if_possible)
      then show False
        using \<open>u \<notin> Vs (step \<sigma>' (ranking_aux \<sigma> us M) u ns)\<close> by linarith
    qed
      

    from not_matched Cons.IH[OF p1 p2 p3 disjoint_step] show ?thesis
      apply (simp add: a_pair step_M step'_M step_append_eq)
      sorry
  qed
qed simp
  

lemma
  assumes "wf_input (\<sigma> @ \<sigma>') us"
  assumes "v \<in> set \<sigma>"
  assumes "{u,v} \<in> ranking \<sigma> us"
  shows "{u,v} \<in> ranking (\<sigma> @ \<sigma>') us"
  sorry


theorem
  assumes wf_input: "wf_input \<sigma> us"
  assumes v_in_set: "v \<in> set \<sigma>"
  assumes w_in_set: "w \<in> set \<sigma>" 
  assumes w_neighbor: "w \<in> neighbors_of u us" 
  assumes w_unmatched: "w \<notin> Vs (ranking \<sigma> us)"
  assumes u_v_match: "{u,v} \<in> ranking \<sigma> us"
  assumes i_less: "i < length \<sigma>"
  assumes v'_match: "{u,v'} \<in> ranking (w \<mapsto>\<^bsub>\<sigma>\<^esub> i) us" \<comment> \<open>this assumption needs to be proven\<close>
  shows "rank (w \<mapsto>\<^bsub>\<sigma>\<^esub> i) v' \<le> rank \<sigma> w"
proof -
  let ?\<sigma>i = "(w \<mapsto>\<^bsub>\<sigma>\<^esub> i)"

  have set_move_to: "set ?\<sigma>i = set \<sigma>" using w_in_set by (auto simp: move_to_set)

  have partitioned_bipartite: "partitioned_bipartite (ranking \<sigma> us) (set \<sigma>)"
    using wf_input
    by (simp add: wf_input_partitioned_bipartite_ranking)

  then have u_in_U: "u \<notin> set \<sigma>"
    using u_v_match v_in_set
    by (auto elim: partitioned_bipartiteE)

  have v_once: "count_list \<sigma> v = 1"
    using wf_input v_in_set
    by (auto dest!: wf_input_distinctD distinct_count_in_set)

  have wf_input_move_to: "wf_input ?\<sigma>i us" 
    using wf_input_move_to[OF wf_input w_in_set]
    by blast

  have matching_move_to: "matching (ranking ?\<sigma>i us)"
    by (simp add: wf_input_move_to wf_input_matching_ranking)

  have partitioned_bipartite_move_to: "partitioned_bipartite (ranking ?\<sigma>i us) (set \<sigma>)"
    using wf_input_move_to
    by (simp add: wf_input_move_to wf_input_partitioned_bipartite_ranking flip: set_move_to)


  have w_in_move: "w \<in> set ?\<sigma>i" by (auto simp: move_to_set)
  have w_rank_i: "rank ?\<sigma>i w = i" 
    using move_to_rank_v wf_input i_less
    by (force dest: wf_input_distinctD)

  have v'_in_set: "v' \<in> set \<sigma>"
    using partitioned_bipartite_move_to u_in_U v'_match
    by (auto elim: partitioned_bipartiteE)

  have rank_v_less_rank_w: "rank \<sigma> v < rank \<sigma> w" 
    using assms ranking_lowest_rank
    by metis

  consider (match_w) "rank ?\<sigma>i w \<le> rank \<sigma> v" | (match_v) "rank \<sigma> v < rank ?\<sigma>i w" by linarith
  then show ?thesis
  proof cases
    case match_w
    have w_match: "v' = w" \<comment> \<open>This is not necessarily true, i.e. when w is matched to some u' before u arrives. The cascading also takes effect here.\<close>
    proof (rule ccontr)
      assume "v' \<noteq> w"
      have "rank ?\<sigma>i v' < rank ?\<sigma>i w" 
        apply (rule ranking_lowest_rank[where u=u and us=us])
             apply (simp add: wf_input_move_to)
            apply (simp_all add: set_move_to v'_in_set w_in_set w_neighbor)
        sorry
      show False sorry
    qed
    then show ?thesis
      using rank_v_less_rank_w w_rank_i match_w by simp
  next
    case match_v
    have "w \<notin> Vs (ranking ?\<sigma>i us)" sorry
    have v_match: "v' = v"
    proof (rule ccontr)
      assume "v' \<noteq> v"
      have "rank ?\<sigma>i v' < rank ?\<sigma>i v"
        apply (rule ranking_lowest_rank[where u=u and us = us])
        sorry
      show False sorry
    qed
    then show ?thesis sorry
  qed
qed

lemma step_filter_offline_eq:
  assumes "x \<notin> Vs (step \<sigma> M u ns)"
  shows "step [v <- \<sigma>. v \<noteq> x] M u ns = step \<sigma> M u ns"
  using assms
proof (induction \<sigma> M u ns rule: step.induct)
  case (2 v vs M u neighbors)
  then show ?case
    by (smt (verit, del_insts) edges_are_Vs filter.simps(2) insertCI insert_commute step.simps(2))
qed simp

lemma step_filter_online_eq:
  assumes "x \<notin> Vs (step \<sigma> M x ns)"
  shows "step \<sigma> M x ns = M"
  using assms
proof (induction \<sigma> M x ns rule: step.induct)
  case (2 v vs M u neighbors)
  then show ?case
    by (metis insertI1 step.simps(2) vs_member)
qed simp

lemma step_filter_online_neighbors_eq:
  assumes "x \<notin> Vs (step \<sigma> M u ns)"
  shows "step \<sigma> M u (ns - {x}) = step \<sigma> M u ns"
  using assms
proof (induction \<sigma> M u ns rule: step.induct)
  case (2 v vs M u neighbors)
  then show ?case
    by (smt (verit, ccfv_threshold) DiffE DiffI insertI1 insert_commute singletonD step.simps(2) vs_member)
qed simp
  

lemma ranking_aux_filter_offline_eq:
  assumes "x \<notin> Vs (ranking_aux \<sigma> us M)"
  shows "ranking_aux [v <- \<sigma>. v \<noteq> x] us M = ranking_aux \<sigma> us M"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u ns us M)
  then have "x \<notin> Vs (step \<sigma> M u ns)"
    by (metis ranking_aux.simps(2) ranking_aux_mono vs_member)
  from step_filter_offline_eq[OF this] have "step [v <- \<sigma>. v \<noteq> x] M u ns = step \<sigma> M u ns" by simp
  with 2 show ?case 
    by simp
qed simp

lemma ranking_aux_filter_online_eq:
  assumes "x \<notin> Vs (ranking_aux \<sigma> us M)"
  shows "ranking_aux \<sigma> [(u,ns) <- us. u \<noteq> x] M = ranking_aux \<sigma> us M"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u ns us M)
  then have x_not_in_step: "x \<notin> Vs (step \<sigma> M u ns)"
    by (metis ranking_aux.simps(2) ranking_aux_mono vs_member)
  then show ?case
  proof (cases "u = x")
    case True
    with x_not_in_step have "step \<sigma> M u ns = M"
      by (metis step_filter_online_eq)
    with 2 show ?thesis by simp
  next
    case False
    with 2 show ?thesis by simp
  qed
qed simp

lemma ranking_aux_filter_online_neighbors_eq:
  assumes "x \<notin> Vs (ranking_aux \<sigma> us M)"
  shows "ranking_aux \<sigma> (map (\<lambda>(u,ns). (u, ns - {x})) us) M = ranking_aux \<sigma> us M"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u ns us M)
  then have "x \<notin> Vs (step \<sigma> M u ns)" 
    by (metis ranking_aux.simps(2) ranking_aux_mono vs_member)
  from step_filter_online_neighbors_eq[OF this] have "step \<sigma> M u (ns - {x}) = step \<sigma> M u ns" by simp
  with 2 show ?case 
    by simp
qed simp

lemma ranking_filter_offline_eq:
  assumes "x \<notin> Vs (ranking \<sigma> us)"
  shows "ranking [v <- \<sigma>. v \<noteq> x] us = ranking \<sigma> us"
  using assms
  by (simp add: ranking_def ranking_aux_filter_offline_eq)

lemma ranking_filter_online_eq:
  assumes "x \<notin> Vs (ranking \<sigma> us)"
  shows "ranking \<sigma> [(u,ns) <- us. u \<noteq> x] = ranking \<sigma> us"
  using assms
  by (simp add: ranking_def ranking_aux_filter_online_eq)

lemma ranking_filter_online_neighbors_eq:
  assumes "x \<notin> Vs (ranking \<sigma> us)"
  shows "ranking \<sigma> (map (\<lambda>(u,ns). (u, ns - {x})) us) = ranking \<sigma> us"
  using assms
  by (simp add: ranking_def ranking_aux_filter_online_neighbors_eq)

lemma ranking_remove_vertex_eq:
  assumes "x \<notin> Vs (ranking \<sigma> us)"
  shows "ranking [v <- \<sigma>. v \<noteq> x] [(u,ns) <- (map (\<lambda>(u,ns). (u, ns - {x})) us). u \<noteq> x] = ranking \<sigma> us"
  using assms
  by (simp add: ranking_filter_offline_eq ranking_filter_online_eq ranking_filter_online_neighbors_eq)


inductive remove_vertex_path :: "'a \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a graph \<Rightarrow> 'a list \<Rightarrow> bool" where
  unmatched:  "x \<notin> Vs M \<Longrightarrow> remove_vertex_path x \<sigma> us M []"
| matched_boy: "{u,x} \<in> M \<Longrightarrow> x \<in> set \<sigma> \<Longrightarrow> u \<in> arriving_U us \<Longrightarrow> remove_vertex_path u \<sigma> us M vs \<Longrightarrow> remove_vertex_path x \<sigma> us M (x#vs)"
| matched_girl: "x \<in> set \<sigma> \<Longrightarrow> u \<in> arriving_U us \<Longrightarrow> {u,x} \<in> offline_graph us 
  \<Longrightarrow> (\<And>x'. x' \<in> set \<sigma>  \<Longrightarrow> rank \<sigma> x' < rank \<sigma> x \<Longrightarrow> {u,x'} \<notin> offline_graph us \<or> (\<exists>u' \<in> arriving_U us. arrival us u' < arrival us u \<and> {u',x'} \<in> M))
  \<Longrightarrow> remove_vertex_path x \<sigma> us M vs \<Longrightarrow> remove_vertex_path u \<sigma> us M (x#vs)"


end
