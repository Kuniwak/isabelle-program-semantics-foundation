theory PFun
  imports Main
begin

typedef ('a, 'b) pfun = "UNIV :: ('a \<Rightarrow> 'b option) set"
  by (rule exI, rule UNIV_I)

instantiation "pfun" :: (type, type) order
begin

definition less_eq_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool"
  where "less_eq_pfun f1 f2 \<equiv> \<forall>x y. Rep_pfun f1 x = Some y \<longrightarrow> Rep_pfun f2 x = Some y"

definition less_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool"
  where "less_pfun s1 s2 \<equiv> s1 \<le> s2 \<and> \<not> s2 \<le> s1"

instance proof
  fix x y :: "('a, 'b) pfun"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_pfun_def by simp
next
  fix x :: "('a, 'b) pfun"
  show "x \<le> x" unfolding less_eq_pfun_def by simp
next
  fix x y z :: "('a, 'b) pfun"
  assume "x \<le> y" "y \<le> z"
  thus "x \<le> z" unfolding less_eq_pfun_def by simp
next
  fix x y :: "('a, 'b) pfun"
  assume 1: "x \<le> y" "y \<le> x"
  show "x = y" proof (cases x)
    case Abs_pfun1: (Abs_pfun f)
    show ?thesis proof (cases y)
      case Abs_pfun2: (Abs_pfun g)
      show ?thesis using 1 unfolding Abs_pfun1 Abs_pfun2 less_eq_pfun_def Abs_pfun_inject[OF UNIV_I UNIV_I] Abs_pfun_inverse[OF UNIV_I] proof -
        assume 1[rule_format]: "\<forall>x y. g x = Some y \<longrightarrow> f x = Some y"
        assume 2[rule_format]: "\<forall>x y. f x = Some y \<longrightarrow> g x = Some y"
        have 3: "\<And>f g. (\<And>x. f x = g x) \<Longrightarrow> f = g" by blast
        show "f = g" proof (rule 3)
          fix v
          show "f v = g v" proof (cases "f v")
            case None
            show ?thesis using 1[of v] unfolding None by fastforce
          next
            case (Some n)
            show ?thesis using 2[of v] unfolding Some by simp
          qed
        qed
      qed
    qed
  qed
qed
end

instantiation "pfun" :: (type, type) order_bot
begin

definition bot_pfun :: "('a, 'b) pfun"
  where "bot_pfun \<equiv> Abs_pfun (\<lambda>_. None)"

instance proof
  fix a :: "('a, 'b) pfun"
  show "bot \<le> a" unfolding bot_pfun_def less_eq_pfun_def Abs_pfun_inverse[OF UNIV_I] by simp
qed
end

(*
instantiation "pfun" :: (ccpo, ccpo) ccpo
begin



end*)

end