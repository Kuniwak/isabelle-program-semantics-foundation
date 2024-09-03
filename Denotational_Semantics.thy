theory Denotational_Semantics
  imports Syntax State
begin


fun denote_arith :: "arith \<Rightarrow> state \<Rightarrow> int option"
  where "denote_arith (AInt n) s = Some n"
      | "denote_arith (AVar v) s = lookup s v"
      | "denote_arith (AAdd a1 a2) s = (case (denote_arith a1 s, denote_arith a2 s)
        of (Some n1, Some n2) \<Rightarrow> Some (n1 + n2)
         | (_, _) \<Rightarrow> None)"
      | "denote_arith (AMult a1 a2) s = (case (denote_arith a1 s, denote_arith a2 s)
        of (Some n1, Some n2) \<Rightarrow> Some (n1 * n2)
         | (_, _) \<Rightarrow> None)"
      | "denote_arith (ASub a1 a2) s = (case (denote_arith a1 s, denote_arith a2 s)
        of (Some n1, Some n2) \<Rightarrow> Some (n1 - n2)
         | (_, _) \<Rightarrow> None)"

fun denote_bexp :: "bexp \<Rightarrow> state \<Rightarrow> bool option"
  where "denote_bexp (BBool b) s = Some b"
      | "denote_bexp (BLessEq a1 a2) s = (case (denote_arith a1 s, denote_arith a2 s)
        of (Some n1, Some n2) \<Rightarrow> Some (n1 \<le> n2)
         | (_, _) \<Rightarrow> None)"
      | "denote_bexp (BNot b) s = (case denote_bexp b s
        of Some b \<Rightarrow> Some (\<not>b)
         | _ \<Rightarrow> None)"
      | "denote_bexp (BAnd b1 b2) s = (case (denote_bexp b1 s, denote_bexp b2 s)
        of (Some b1, Some b2) \<Rightarrow> Some (b1 \<and> b2)
         | (_, _) \<Rightarrow> None)"

fun denote_prog_step :: "prog \<Rightarrow> (state, state) pfun \<Rightarrow> (state, state) pfun"
  where "denote_prog_step PSkip _ = Abs_pfun (\<lambda>s. Some s)"
      | "denote_prog_step (PAssg v a) _ = Abs_pfun (\<lambda>s. case denote_arith a s
        of Some n \<Rightarrow> Some (state_upd s v (Some n))
         | None \<Rightarrow> None)"
      | "denote_prog_step (PSeq p1 p2) f = Abs_pfun (\<lambda>s. case Rep_pfun (denote_prog_step p1 f) s
        of Some s' \<Rightarrow> Rep_pfun (denote_prog_step p2 f) s'
         | None \<Rightarrow> None)"
      | "denote_prog_step (PIf b p1 p2) f = Abs_pfun (\<lambda>s. case denote_bexp b s
        of Some True \<Rightarrow> Rep_pfun (denote_prog_step p1 f) s
         | Some False \<Rightarrow> Rep_pfun (denote_prog_step p2 f) s
         | None \<Rightarrow> None)"
      | "denote_prog_step (PWhile b p) f = Abs_pfun (\<lambda>s. case denote_bexp b s
        of Some True \<Rightarrow> (case Rep_pfun (denote_prog_step p f) s
          of Some s' \<Rightarrow> (Rep_pfun f) s
           | None \<Rightarrow> None)
         | Some False \<Rightarrow> Some s
         | None \<Rightarrow> None)"

lemma mono_denote_prog_step: "mono (denote_prog_step p)"
proof
  fix x y :: "(state, state) pfun"
  assume "x \<le> y"
  thus "denote_prog_step p x \<le> denote_prog_step p y" unfolding less_eq_pfun_def proof auto
    fix z w :: state
    assume "\<forall>u v. Rep_pfun x u = Some v \<longrightarrow> Rep_pfun y u = Some v"
      and "Rep_pfun (denote_prog_step p x) z = Some w"
    thus "Rep_pfun (denote_prog_step p y) z = Some w" proof (induction p arbitrary: z w)
      case PSkip
      thus ?case by simp
    next
      case (PAssg x1 x2)
      thus ?case by simp
    next
      case (PSeq p1 p2)
      thus ?case proof (simp add: Abs_pfun_inverse[OF UNIV_I])
        assume 1: "(case Rep_pfun (denote_prog_step p1 x) z of None \<Rightarrow> None | Some xa \<Rightarrow> Rep_pfun (denote_prog_step p2 x) xa) = Some w"
        then obtain a where 2: "Rep_pfun (denote_prog_step p1 x) z = Some a" by fastforce
        assume "\<And>z w. Rep_pfun (denote_prog_step p1 x) z = Some w \<Longrightarrow> Rep_pfun (denote_prog_step p1 y) z = Some w"
        hence 3: "Rep_pfun (denote_prog_step p1 y) z = Some a" using 2 by blast
        have 4: "Rep_pfun (denote_prog_step p2 x) a = Some w" using 1 2 by fastforce
        assume "\<And>z w. Rep_pfun (denote_prog_step p2 x) z = Some w \<Longrightarrow> Rep_pfun (denote_prog_step p2 y) z = Some w"
        hence 5: "Rep_pfun (denote_prog_step p2 y) a = Some w" using 4 by blast
        show "(case Rep_pfun (denote_prog_step p1 y) z of None \<Rightarrow> None | Some x \<Rightarrow> Rep_pfun (denote_prog_step p2 y) x) = Some w" unfolding 3 using 5 by simp
      qed
    next
      case (PIf b p1 p2)
      thus ?case proof (simp add: Abs_pfun_inverse[OF UNIV_I])
        assume 1: "(case denote_bexp b z of None \<Rightarrow> None | Some True \<Rightarrow> Rep_pfun (denote_prog_step p1 x) z | Some False \<Rightarrow> Rep_pfun (denote_prog_step p2 x) z) = Some w"
        then obtain v where 2: "denote_bexp b z = Some v" by fastforce
        assume 3: "\<And>z w. Rep_pfun (denote_prog_step p1 x) z = Some w \<Longrightarrow> Rep_pfun (denote_prog_step p1 y) z = Some w"
          and 4: "\<And>z w. Rep_pfun (denote_prog_step p2 x) z = Some w \<Longrightarrow> Rep_pfun (denote_prog_step p2 y) z = Some w"
        show "(case denote_bexp b z of None \<Rightarrow> None | Some True \<Rightarrow> Rep_pfun (denote_prog_step p1 y) z | Some False \<Rightarrow> Rep_pfun (denote_prog_step p2 y) z) = Some w" proof (cases v)
          case True
          hence "Rep_pfun (denote_prog_step p1 x) z = Some w" using 1 unfolding 2 by simp
          hence "Rep_pfun (denote_prog_step p1 y) z = Some w" using 3 by blast
          thus ?thesis unfolding 2 using True by simp
        next
          case False
          hence "Rep_pfun (denote_prog_step p2 x) z = Some w" using 1 unfolding 2 by simp
          hence "Rep_pfun (denote_prog_step p2 y) z = Some w" using 4 by blast
          thus ?thesis unfolding 2 using False by simp
        qed
      qed
    next
      case (PWhile b p)
      thus ?case proof (simp add: Abs_pfun_inverse[OF UNIV_I])
        assume 1: "(case denote_bexp b z of None \<Rightarrow> None | Some True \<Rightarrow> (case Rep_pfun (denote_prog_step p x) z of None \<Rightarrow> None | Some s' \<Rightarrow> Rep_pfun x z) | Some False \<Rightarrow> Some z) = Some w"
        then obtain a where 2: "denote_bexp b z = Some a" by fastforce
        assume 3: "\<And>z w. Rep_pfun (denote_prog_step p x) z = Some w \<Longrightarrow> Rep_pfun (denote_prog_step p y) z = Some w"
          and 4[rule_format]: "\<forall>u v. Rep_pfun x u = Some v \<longrightarrow> Rep_pfun y u = Some v"
        show "(case denote_bexp b z of None \<Rightarrow> None | Some True \<Rightarrow> (case Rep_pfun (denote_prog_step p y) z of None \<Rightarrow> None | Some s' \<Rightarrow> Rep_pfun y z) | Some False \<Rightarrow> Some z) = Some w" proof (cases a)
          case True
          have "(case Rep_pfun (denote_prog_step p x) z of None \<Rightarrow> None | Some s' \<Rightarrow> Rep_pfun x z) = Some w" using 1 unfolding 2 using True by simp
          then obtain s' where 5: "Rep_pfun (denote_prog_step p x) z = Some s'" by fastforce
          hence 6: "Rep_pfun (denote_prog_step p y) z = Some s'" using 3[of z s'] by simp
          show ?thesis using 1 unfolding 2 5 6 using 4 True by simp
        next
          case False
          hence 5: "z = w" using 1 unfolding 2 by simp
          show ?thesis unfolding 2 unfolding 5 using False by simp
        qed
      qed
    qed
  qed
qed

fun denote_prog_n :: "prog \<Rightarrow> nat \<Rightarrow> (state, state) pfun"
  where "denote_prog_n p n = ((denote_prog_step p) ^^ n) bot"

lemma mono_funpow_bot:
  fixes f :: "('a :: order_bot) \<Rightarrow> 'a"
  assumes "mono f"
  shows "mono (\<lambda>n. (f ^^ n) bot)"
  by (simp add: assms funpow_mono2 monoI)

lemma mono_denote_prog_n: "mono (denote_prog_n p)"
  using mono_denote_prog_step unfolding denote_prog_n.simps by (rule mono_funpow_bot)

definition denote_prog :: "prog \<Rightarrow> (state, state) pfun"
  where "denote_prog p \<equiv> Sup {denote_prog_n p n |n. True}"

end